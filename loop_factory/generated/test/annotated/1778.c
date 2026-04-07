int main1(int p){
  int s, zf, jl, hl;
  s=(p%60)+60;
  zf=(p%9)+2;
  jl=0;
  hl=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= jl);
  loop invariant zf*jl + hl <= s;
  loop invariant p == \at(p, Pre);
  loop invariant s == ((\at(p, Pre) % 60) + 60);
  loop invariant 0 <= hl;
  loop invariant zf == ((\at(p, Pre)) % 9) + 2;
  loop assigns hl, jl, p;
*/
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