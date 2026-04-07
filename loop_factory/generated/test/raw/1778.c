int main1(int p){
  int s, zf, jl, hl;

  s=(p%60)+60;
  zf=(p%9)+2;
  jl=0;
  hl=0;

  while (1) {
      if (s<=zf*jl+hl) {
          break;
      }
      if (hl==zf-1) {
          hl = 0;
          jl++;
      }
      else {
          hl += 1;
      }
      p = p+jl-jl;
  }

}
