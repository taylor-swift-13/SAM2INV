int main1(int a,int q){
  int c, j, t, e;

  c=20;
  j=0;
  t=3;
  e=q;


while (1) {
      if (j>=c) {
          break;
      }
      t = t+3;
      j = j+1;
      t = t+1;
      e = e-1;
      if ((j%5)==0) {
          e = e+1;
      }
  }
/*@
  assert (t == 3 + 4*j);
*/

  while (t > c) {
      if (j > 0 && t - j >= c) {
          t = t - j;
          j = j / 2;
      } else {
          t = t - 1;
      }
      e = e + 1;
  }
/*@
  assert !(t > c) &&
         (t == c);
*/
}
