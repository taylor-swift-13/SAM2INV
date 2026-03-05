int main130(int o,int e,int x){
  int qvu, g51, ty;

  qvu=(x%19)+15;
  g51=0;
  ty=1;

  while (1) {
      if (ty==1) {
          ty = 2;
      }
      else {
          if (ty==2) {
              ty = 1;
          }
      }
      e = e + ty;
      o += 2;
      o = o + 1;
      g51++;
      if (g51>=qvu) {
          break;
      }
  }

}
