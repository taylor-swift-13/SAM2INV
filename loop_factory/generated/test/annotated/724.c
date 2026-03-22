int main1(){
  int q, m8, g7, m, l1;
  q=1+10;
  m8=q;
  g7=(1%40)+2;
  m=0;
  l1=m8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == 11;
  loop invariant l1 == 11;
  loop invariant g7 > 0;
  loop invariant m >= 0;
  loop assigns m, g7, l1;
*/
while (g7!=m) {
      m = g7;
      g7 = (g7+q/g7)/2;
      l1 = l1+m-m;
  }
}