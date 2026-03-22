int main1(int k,int d){
  int m3fi, y0a;
  m3fi=k*2;
  y0a=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m3fi == 2 * k;
  loop invariant 0 <= y0a;
  loop invariant (m3fi < 0) || (y0a <= m3fi);
  loop invariant m3fi == 2 * \at(k, Pre);
  loop assigns y0a;
*/
while (1) {
      if (!(y0a<m3fi)) {
          break;
      }
      y0a += 1;
  }
}