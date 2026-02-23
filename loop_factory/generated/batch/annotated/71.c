int main1(int k,int p){
  int c, m, j, b, a;

  c=k;
  m=0;
  j=k;
  b=p;
  a=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == p;
  loop invariant b == p + a * m;
  loop invariant c == \at(k, Pre);

  loop invariant p == \at(p, Pre);
  loop invariant a == \at(p, Pre);
  loop invariant b == \at(p, Pre) + m * a;
  loop invariant m >= 0;
  loop invariant (c >= 0) ==> m <= c;
  loop invariant c == k;
  loop invariant 0 <= m;
  loop invariant b == a * m + \at(p, Pre);

  loop invariant k == \at(k, Pre);
  loop invariant b == p*(m+1);
  loop assigns b, m;
*/
while (m<c) {
      b = b+a;
      m = m+1;
  }

}
