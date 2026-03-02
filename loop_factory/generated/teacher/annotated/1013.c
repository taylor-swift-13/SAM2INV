int main1(int b,int m){
  int a, q, e, v;

  a=b;
  q=0;
  e=a;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(b, Pre);
  loop invariant m == \at(m, Pre);

  loop invariant (a > 0 ==> e >= a) && (a < 0 ==> e <= a);

  loop invariant a == 0 ==> e == 0;
  loop invariant \at(m, Pre) == 0 ==> v == 0;
  loop invariant b == \at(b, Pre);
  loop invariant b == \at(b, Pre) && m == \at(m, Pre);

  loop invariant \at(b, Pre) >= 0 && \at(m, Pre) >= 0 ==> (0 <= v && v <= \at(m, Pre) && e * v <= \at(b, Pre) * \at(m, Pre));

  loop assigns e, v;
*/
while (1) {
      e = e*2;
      v = v/2;
  }

}
