/*
 * MiniASTConsumer collects identifiers in `used` and rename candidates (in the main file) in `d2name`.
 * MiniASTConsumer iterates over `d2name` and assigns new names.
 * Renamer creates clang::tooling::Replacement instances.
 * HandleTranslationUnit calls clang::tooling::applyAllReplacements.
 */

// clang-format: off
#undef NDEBUG
#include <cassert>
// clang-format: on

#include <clang/AST/ASTConsumer.h>
#include <clang/AST/Decl.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/Basic/FileManager.h>
#include <clang/Basic/LangOptions.h>
#include <clang/Basic/SourceManager.h>
#include <clang/Basic/TargetInfo.h>
#include <clang/Driver/Action.h>
#include <clang/Driver/Compilation.h>
#include <clang/Driver/Driver.h>
#include <clang/Driver/Tool.h>
#include <clang/Format/Format.h>
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Frontend/FrontendAction.h>
#include <clang/Lex/Lexer.h>
#include <clang/Lex/PreprocessorOptions.h>
#include <clang/Tooling/Core/Replacement.h>
#include <llvm/ADT/CachedHashString.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/MapVector.h>
#include <llvm/ADT/STLExtras.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/TargetParser/Host.h>

#include <memory>
#include <vector>

#include <err.h>
#include <unistd.h>

using namespace clang;
using namespace llvm;

namespace {
std::unique_ptr<CompilerInvocation> buildCompilerInvocation(ArrayRef<const char *> args) {
  IntrusiveRefCntPtr<DiagnosticsEngine> diags(
      CompilerInstance::createDiagnostics(new DiagnosticOptions, new IgnoringDiagConsumer, true));

  clang::driver::Driver d{args[0], llvm::sys::getDefaultTargetTriple(), *diags, "cminify",
                          llvm::vfs::getRealFileSystem()};
  d.setCheckInputsExist(false);
  std::unique_ptr<clang::driver::Compilation> comp(d.BuildCompilation(args));
  if (!comp)
    return nullptr;
  const clang::driver::JobList &jobs = comp->getJobs();
  if (jobs.size() != 1 || !isa<clang::driver::Command>(*jobs.begin()))
    return nullptr;

  const clang::driver::Command &cmd = cast<clang::driver::Command>(*jobs.begin());
  if (StringRef(cmd.getCreator().getName()) != "clang")
    return nullptr;
  const llvm::opt::ArgStringList &cc_args = cmd.getArguments();
  auto ci = std::make_unique<CompilerInvocation>();
  if (!CompilerInvocation::CreateFromArgs(*ci, cc_args, *diags))
    return nullptr;

  ci->getDiagnosticOpts().IgnoreWarnings = true;
  ci->getFrontendOpts().DisableFree = false;
  return ci;
}

SmallVector<StringRef, 0> ignores;
MapVector<Decl *, std::string> d2name;
DenseSet<CachedHashStringRef> used;
std::string newCode;

struct Collector : RecursiveASTVisitor<Collector> {
  SourceManager &sm;

  Collector(ASTContext &ctx) : sm(ctx.getSourceManager()) {}
  bool VisitFunctionDecl(FunctionDecl *fd) {
    if (fd->isOverloadedOperator() || !fd->getIdentifier())
      return true;
    used.insert(CachedHashStringRef(fd->getName()));
    if (!fd->isDefined())
      return true;
    std::string name = fd->getNameAsString();
    if (sm.isWrittenInMainFile(fd->getLocation())) {
      if (!is_contained(ignores, name))
        d2name[fd->getCanonicalDecl()] = "_f";
      for (ParmVarDecl *param : fd->parameters())
        VisitVarDecl(param);
    }
    return true;
  }
  bool VisitVarDecl(VarDecl *vd) {
    if (!vd->getIdentifier())
      return true;
    used.insert(CachedHashStringRef(vd->getName()));
    auto kind = vd->isThisDeclarationADefinition();
    if (kind != VarDecl::Definition || !sm.isWrittenInMainFile(vd->getLocation()))
      return true;
    d2name[vd->getCanonicalDecl()] = "_v";
    return true;
  }

  bool VisitTagDecl(TagDecl *td) {
    used.insert(CachedHashStringRef(td->getName()));
    if (!td->isThisDeclarationADefinition() || !sm.isWrittenInMainFile(td->getLocation()))
      return true;
    d2name[td->getCanonicalDecl()] = "_t";
    return true;
  }
  bool VisitTypedefNameDecl(TypedefNameDecl *d) {
    if (d->isTransparentTag() || !sm.isWrittenInMainFile(d->getLocation()))
      return true;
    d2name[d->getCanonicalDecl()] = "_t";
    return true;
  }
};

struct Renamer : RecursiveASTVisitor<Renamer> {
  SourceManager &sm;
  tooling::Replacements &reps;

  Renamer(ASTContext &ctx, tooling::Replacements &reps) : sm(ctx.getSourceManager()), reps(reps) {}
  void replace(CharSourceRange csr, StringRef newText) { cantFail(reps.add(tooling::Replacement(sm, csr, newText))); }

  bool VisitFunctionDecl(FunctionDecl *fd) {
    auto *canon = fd->getCanonicalDecl();
    auto it = d2name.find(canon);
    if (it != d2name.end())
      replace(CharSourceRange::getTokenRange(fd->getLocation()), it->second);
    return true;
  }
  bool VisitVarDecl(VarDecl *vd) {
    auto *canon = vd->getCanonicalDecl();
    auto it = d2name.find(canon);
    if (it != d2name.end())
      replace(CharSourceRange::getTokenRange(vd->getLocation()), it->second);
    return true;
  }
  bool VisitDeclRefExpr(DeclRefExpr *dre) {
    Decl *d = dre->getDecl();
    if (!(isa<FunctionDecl>(d) || isa<VarDecl>(d)))
      return true;
    auto it = d2name.find(d->getCanonicalDecl());
    if (it != d2name.end())
      replace(CharSourceRange::getTokenRange(SourceRange(dre->getBeginLoc(), dre->getEndLoc())), it->second);
    return true;
  }

  bool VisitTagDecl(TagDecl *d) {
    auto *canon = d->getCanonicalDecl();
    if (d->getTypedefNameForAnonDecl())
      return true;
    if (auto it = d2name.find(canon); it != d2name.end())
      replace(CharSourceRange::getTokenRange(d->getLocation()), it->second);
    return true;
  }
  bool VisitTagTypeLoc(TagTypeLoc tl) {
    TagDecl *td = tl.getDecl()->getCanonicalDecl();
    if (td->getTypedefNameForAnonDecl())
      return true;
    if (auto it = d2name.find(td); it != d2name.end())
      replace(CharSourceRange::getTokenRange(tl.getNameLoc()), it->second);
    return true;
  }
  bool VisitTypedefNameDecl(TypedefNameDecl *d) {
    if (auto it = d2name.find(d->getCanonicalDecl()); it != d2name.end())
      replace(CharSourceRange::getTokenRange(d->getLocation()), it->second);
    return true;
  }
  bool VisitTypedefTypeLoc(TypedefTypeLoc tl) {
    TypedefNameDecl *td = tl.getTypedefNameDecl();
    if (auto it = d2name.find(td); it != d2name.end())
      replace(CharSourceRange::getTokenRange(tl.getNameLoc()), it->second);
    return true;
  }
};

class MiniASTConsumer : public ASTConsumer {
public:
  MiniASTConsumer(bool remove_comments = false, bool rename_symbols = false)
      : m_remove_comments{remove_comments}, m_rename_symbols{rename_symbols} {}

  void Initialize(ASTContext &ctx) override { this->ctx = &ctx; }
  static std::string getName(StringRef prefix, int &id) {
    static const char digits[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
    std::string newName;
    for (;;) {
      newName = std::string(1, prefix[id % prefix.size()]);
      if (int i = id / prefix.size())
        while (newName += digits[i % 62], i /= 62)
          ;
      id++;
      if (!used.contains(CachedHashStringRef(newName)))
        break;
    }
    return newName;
  }
  bool HandleTopLevelDecl(DeclGroupRef dgr) override {
    if (m_rename_symbols) {
      for (auto s : {"j0", "j1", "jn", "j0f", "j1f", "jnf", "j0l", "j1l", "jnl"})
        used.insert(CachedHashStringRef(s));
      for (auto s : {"y0", "y1", "yn", "y0f", "y1f", "ynf", "y0l", "y1l", "ynl"})
        used.insert(CachedHashStringRef(s));

      Collector c(*ctx);
      for (Decl *d : dgr)
        c.TraverseDecl(d);
      for (auto &[d, name] : d2name) {
        if (name == "_f")
          name = getName("abcdefghijklm", n_fn);
        else if (name == "_v") {
          int old_n_var = n_var;
          auto newName = getName("nopqrstuvwxyz", n_var);
          if (newName.size() < static_cast<VarDecl *>(d)->getName().size())
            name = newName;
          else {
            name = static_cast<VarDecl *>(d)->getName();
            n_var = old_n_var;
          }
        } else if (name == "_t")
          name = getName("ABCDEFGHIJKLMNOPQRSTUVWXYZ", n_type);
      }
    }
    return true;
  }
  void HandleTranslationUnit(ASTContext &ctx) override {
    tooling::Replacements reps;

    if (m_rename_symbols) {
      Renamer c(ctx, reps);
      c.TraverseDecl(ctx.getTranslationUnitDecl());
    }

    auto &sm = ctx.getSourceManager();
    StringRef code = sm.getBufferData(sm.getMainFileID());
    auto res = tooling::applyAllReplacements(code, reps);
    if (!res)
      errx(2, "failed to apply replacements: %s", toString(res.takeError()).c_str());
    newCode = *res;
  }

private:
  ASTContext *ctx;
  int n_fn = 0, n_var = 0, n_type = 0;
  const bool m_remove_comments;
  const bool m_rename_symbols;
};

class MiniAction : public ASTFrontendAction {
public:
  MiniAction(unsigned indent_width = 0, unsigned column_limit = 9999, bool remove_comments = false,
             bool rename_symbols = false, bool space_before_assignment = false)
      : m_indent_width{indent_width}, m_column_limit{column_limit}, m_remove_comments{remove_comments},
        m_rename_symbols{rename_symbols}, m_space_before_assignment{space_before_assignment} {}
  unsigned indent_width() const { return m_indent_width; }
  unsigned column_limit() const { return m_column_limit; }
  bool remove_comments() const { return m_remove_comments; }
  bool rename_symbols() const { return m_rename_symbols; }
  bool space_before_assignment() const { return m_space_before_assignment; }
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &ci, StringRef inFile) override {
    return std::make_unique<MiniASTConsumer>();
  }

private:
  const unsigned m_indent_width;
  const unsigned m_column_limit;
  const bool m_remove_comments;
  const bool m_rename_symbols;
  const bool m_space_before_assignment;
};

void reformat(const MiniAction &action) {
  auto buf = MemoryBuffer::getMemBuffer(newCode, "", true);
  format::FormatStyle style = cantFail(format::getStyle("LLVM", "-", "LLVM", newCode, nullptr));
  style.ColumnLimit = action.column_limit();
  style.IndentWidth = action.indent_width();
  style.TabWidth = action.indent_width();
  style.UseTab = format::FormatStyle::UT_Always;
  style.ContinuationIndentWidth = action.indent_width();
  style.SpaceBeforeAssignmentOperators = action.space_before_assignment();
  style.SpaceBeforeParens = format::FormatStyle::SBPO_Never;
  style.AlignEscapedNewlines = format::FormatStyle::ENAS_DontAlign;
  style.AllowShortBlocksOnASingleLine = format::FormatStyle::SBS_Always;
  style.AllowShortFunctionsOnASingleLine = format::FormatStyle::SFS_All;
  style.AllowShortCaseLabelsOnASingleLine = true;
  style.AllowShortEnumsOnASingleLine = true;
  style.AllowShortIfStatementsOnASingleLine = format::FormatStyle::SIS_AllIfsAndElse;
  style.AllowShortLambdasOnASingleLine = format::FormatStyle::SLS_All;
  style.AllowShortLoopsOnASingleLine = true;
  style.AlignConsecutiveAssignments = format::FormatStyle::AlignConsecutiveStyle{.Enabled = false};
  style.AlignConsecutiveDeclarations = format::FormatStyle::AlignConsecutiveStyle{.Enabled = false};
  style.AlignConsecutiveMacros = format::FormatStyle::AlignConsecutiveStyle{.Enabled = false};
  style.AlignConsecutiveBitFields = format::FormatStyle::AlignConsecutiveStyle{.Enabled = false};
  style.AlignArrayOfStructures = format::FormatStyle::AIAS_None;
  style.AlignAfterOpenBracket = format::FormatStyle::BAS_DontAlign;
  style.AlignConsecutiveShortCaseStatements = format::FormatStyle::ShortCaseStatementsAlignmentStyle{.Enabled = false};
  style.AlignEscapedNewlines = format::FormatStyle::ENAS_DontAlign;
  style.AlignOperands = format::FormatStyle::OAS_DontAlign;
  style.AlignTrailingComments =
      format::FormatStyle::TrailingCommentsAlignmentStyle{.Kind = format::FormatStyle::TCAS_Never};
  style.AllowAllArgumentsOnNextLine = true;
  // style.AllowShortCaseExpressionOnASingleLine = true; // clang-format 19
  style.BinPackArguments = true;
  style.BinPackParameters = true;
  style.BitFieldColonSpacing = format::FormatStyle::BFCS_None;
  style.BraceWrapping =
      format::FormatStyle::BraceWrappingFlags{.AfterCaseLabel = false,
                                              .AfterClass = false,
                                              .AfterControlStatement = format::FormatStyle::BWACS_Never,
                                              .AfterEnum = false,
                                              .AfterFunction = false,
                                              .AfterNamespace = false,
                                              .AfterObjCDeclaration = false,
                                              .AfterStruct = false,
                                              .AfterUnion = false,
                                              .AfterExternBlock = false,
                                              .BeforeCatch = false,
                                              .BeforeElse = false,
                                              .BeforeLambdaBody = false,
                                              .BeforeWhile = false,
                                              .IndentBraces = false,
                                              .SplitEmptyFunction = false,
                                              .SplitEmptyRecord = false,
                                              .SplitEmptyNamespace = false};
  style.BreakStringLiterals = false;
  style.BreakAdjacentStringLiterals = false;
  // style.BreakBinaryOperations = format::FormatStyle::BBO_Never; // clang-format 20

  format::FormattingAttemptStatus status;
  std::vector<tooling::Range> ranges{{0, unsigned(newCode.size())}};
  tooling::Replacements reps = format::reformat(style, newCode, ranges, "-", &status);
  auto res = tooling::applyAllReplacements(newCode, reps);
  if (!res)
    errx(2, "failed to apply replacements: %s", toString(res.takeError()).c_str());
  newCode = *res;
}
} // namespace

int main(int argc, char *argv[]) {
  std::vector<const char *> args{argv[0], "-fsyntax-only"};
  bool inplace = false;
  bool rename_syms = false;
  bool remove_comments = false;
  bool space_before_assignment = false;
  unsigned indent = 0;
  unsigned columns = 9999;
  const char *outfile = "/dev/stdout";
  const char usage[] = R"(Usage: %s [-i] [-r] [-c] [-a] [-I <indent>] [-C <column>] [-f fun]... a.c

Options:
-i      edit a.c in place
-r      rename symbols (default: false)
-c      remove comments (default: false)
-a      space before assignment operators (default: false)
-I      indent width (default: 0)
-C      column limit (default: 9999)
-f      ignore function (can be repeated)
)";
  for (int i = 1; i < argc; i++) {
    StringRef opt(argv[i]);
    if (opt[0] != '-')
      args.push_back(argv[i]);
    else if (opt == "-h") {
      printf(usage, getprogname());
      return 0;
    } else if (opt == "-i")
      inplace = true;
    else if (opt == "-r")
      rename_syms = true;
    else if (opt == "-c")
      remove_comments = true;
    else if (opt == "-a")
      space_before_assignment = true;
    else if (opt == "-I" && i + 1 < argc) {
      auto sindent = atoi(argv[++i]);
      assert(sindent >= 0);
      indent = static_cast<unsigned>(sindent);
    } else if (opt == "-C" && i + 1 < argc) {
      auto scol = atoi(argv[++i]);
      assert(scol >= 0);
      columns = static_cast<unsigned>(scol);
    } else if (opt == "-f" && i + 1 < argc)
      ignores.push_back(argv[++i]);
    else if (opt == "-o" && i + 1 < argc)
      outfile = argv[++i];
    else {
      fprintf(stderr, usage, getprogname());
      return 1;
    }
  }
  ignores.push_back("main");

  auto ci = buildCompilerInvocation(args);
  if (!ci)
    errx(1, "failed to build CompilerInvocation");

  auto inst = std::make_unique<CompilerInstance>(std::make_shared<PCHContainerOperations>());
  IgnoringDiagConsumer dc;
  inst->setInvocation(std::move(ci));
  inst->createDiagnostics(&dc, false);
  inst->getDiagnostics().setIgnoreAllWarnings(true);
  inst->setTarget(TargetInfo::CreateTargetInfo(inst->getDiagnostics(), inst->getInvocation().TargetOpts));
  if (!inst->hasTarget())
    errx(1, "hasTarget returns false");
  inst->createFileManager(llvm::vfs::getRealFileSystem());
  inst->setSourceManager(new SourceManager(inst->getDiagnostics(), inst->getFileManager(), true));

  MiniAction action{indent, columns, remove_comments, rename_syms, space_before_assignment};
  if (!action.BeginSourceFile(*inst, inst->getFrontendOpts().Inputs[0]))
    errx(2, "failed to parse");
  if (Error e = action.Execute())
    errx(2, "failed to execute");
  action.EndSourceFile();
  reformat(action);

  std::error_code ec;
  raw_fd_ostream(inplace ? inst->getFrontendOpts().Inputs[0].getFile() : outfile, ec, sys::fs::OF_None) << newCode;
}
