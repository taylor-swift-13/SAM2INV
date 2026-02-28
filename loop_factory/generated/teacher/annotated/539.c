int main1(int b,int m){
  int l, k, e;

  l=m;
  k=0;
  e=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 0;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant l == m;
  loop invariant e >= m;
  loop assigns e;
*/
while (1) {
      e = e+2;
      if ((k%4)==0) {
          e = e*e;
      }
      e = e*e;
  }

}
