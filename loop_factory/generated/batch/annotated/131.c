int main1(int m){
  int b, i, k;

  b=m;
  i=b;
  k=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == m;
  loop invariant k + i*(i+1)/2 == \at(m, Pre) + \at(m, Pre)*(\at(m, Pre)+1)/2;
  loop invariant b == \at(m,Pre);
  loop invariant 2*k == (\at(m,Pre) * \at(m,Pre) + 3 * \at(m,Pre) - i * i - i);

  loop invariant m == \at(m, Pre);
  loop invariant k >= i;
  loop invariant 2*k + i*(i+1) == 2*b + b*(b+1);

  loop invariant i <= b;
  loop invariant k + i*(i+1)/2 == \at(m, Pre) + (\at(m, Pre)*(\at(m, Pre)+1))/2;
  loop invariant i <= \at(m, Pre);
  loop invariant \at(m, Pre) >= 0 ==> i >= 0;
  loop assigns k, i;
*/
while (i>0) {
      k = k+i;
      i = i-1;
  }

}
