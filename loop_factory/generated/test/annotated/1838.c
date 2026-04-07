int main1(){
  int uv, pfw, ug, hl, vn4;
  uv=1;
  pfw=0;
  ug=uv;
  hl=uv;
  vn4=ug * ug;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vn4 == pfw + 1;
  loop invariant ug == 1 + pfw * (pfw + 1) / 2;
  loop invariant hl == 1;
  loop invariant pfw <= uv;
  loop invariant 0 <= pfw;
  loop assigns pfw, vn4, ug, hl;
*/
while (pfw < uv) {
      pfw = pfw + 1;
      vn4++;
      ug = ug + pfw;
      hl = hl*hl;
  }
}