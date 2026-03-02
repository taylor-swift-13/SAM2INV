int main1(int b,int q){
  int m, j, i, f;

  m=b-5;
  j=m+3;
  i=0;
  f=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == b * f && 0 <= f && (m < 0 || f <= m);
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant m == \at(b, Pre) - 5;
  loop invariant i == b * f;

  loop invariant f >= 0;
  loop invariant i == b * f && f >= 0;
  loop invariant m == \at(b, Pre) - 5 && b == \at(b, Pre) && q == \at(q, Pre);
  loop invariant i == f * b;
  loop invariant i == b*f;
  loop invariant 0 <= f;
  loop invariant m == b - 5;
  loop invariant f <= m || f == 0;

  loop assigns i, f;
*/
while (f<m) {
      i = i+b;
      f = f+1;
  }

}
