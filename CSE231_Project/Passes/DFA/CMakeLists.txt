add_llvm_library( CSE231 MODULE
  MayPointToAnalysis.cpp
  
  PLUGIN_TOOL
  opt
  )
