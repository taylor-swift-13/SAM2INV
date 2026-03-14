int main1(int f,int a){
  int f6, yj, g9au, fbq;
  f6=f;
  yj=f6;
  g9au=0;
  fbq=a;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f6 == \at(f, Pre);
  loop invariant g9au >= 0;
  loop invariant f - f6 == g9au * (g9au + 1) / 2;
  loop assigns f, fbq, g9au;
*/
while (g9au<f6) {
      fbq = f6-g9au;
      g9au += 1;
      f += g9au;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g9au >= yj;
  loop assigns yj, f, f6;
*/
while (1) {
      if (!(yj<g9au)) {
          break;
      }
      yj += 1;
      f += g9au;
      f6 = g9au-yj;
  }
}