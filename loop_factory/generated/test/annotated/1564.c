int main1(){
  int s7b, v0ws, d4, fli, mv, yj, p68, zv;
  s7b=1*4;
  v0ws=0;
  d4=15;
  fli=12;
  mv=0;
  yj=0;
  p68=-6;
  zv=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d4 + 2*v0ws == 15;
  loop invariant p68 == v0ws*v0ws + 13*v0ws - 6;
  loop invariant mv == 0;
  loop invariant yj == 4 * v0ws;
  loop invariant d4 + fli == 27;
  loop invariant 0 <= v0ws <= s7b;
  loop invariant zv == 12;
  loop assigns d4, fli, mv, v0ws, zv, yj, p68;
*/
while (v0ws<s7b) {
      if (!(mv!=0)) {
          d4 -= 2;
          fli += 2;
          mv = 0;
      }
      else {
          d4 += 2;
          fli -= 2;
          mv = 1;
      }
      v0ws++;
      if (zv+1<s7b) {
          zv = p68-zv;
      }
      yj = yj + 3;
      p68 = p68 + fli;
      yj += 1;
  }
}