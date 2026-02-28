int main1(int b,int k){
  int i, m, e, a;

  i=46;
  m=0;
  e=m;
  a=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == 6*m;
  loop invariant m >= 0;
  loop invariant a >= 2;
  loop invariant i == 46;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant a >= 2*m + 2;
  loop invariant a >= 0;
  loop invariant a % 2 == 0;
  loop assigns e, a, m;
*/
while (1) {
      e = e+5;
      a = a+e;
      a = a+a;
      e = e+1;
      a = a+e;
      m = m+1;
  }

}
