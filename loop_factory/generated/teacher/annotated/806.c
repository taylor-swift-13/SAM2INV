int main1(int a,int m){
  int g, x, b;

  g=m;
  x=0;
  b=x;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == 0;
  loop invariant g == m;
  loop invariant m == \at(m, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant b >= 0;
  loop invariant b % 3 == 0;
  loop assigns b;
*/
while (1) {
      b = b+2;
      b = b+1;
      if ((x%5)==0) {
          b = b+x;
      }
  }

}
