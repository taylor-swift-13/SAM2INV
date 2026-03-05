int main106(int o,int s){
  int aka, c, ofp, vm, ii;

  aka=o+16;
  c=2;
  ofp=o;
  vm=c;
  ii=-2;

  while (1) {
      if (!(c<aka)) {
          break;
      }
      ofp = ofp + 3;
      c = c + 1;
      vm = vm+aka-c;
      ii = ii + vm;
      s++;
      o = o + ofp;
  }

}
