int main1(int n,int q){
  int s, i, g, v, k;

  s=14;
  i=s;
  g=q;
  v=i;
  k=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g + 5*i == \at(q, Pre) + 70;
  loop invariant i >= 0;
  loop invariant i <= s;
  loop invariant v == s + (s - i) * \at(q, Pre) + 5 * (s - i) * (s - i + 1) / 2;
  loop invariant g <= \at(q, Pre) + 5 * s;
  loop invariant i <= 14;
  loop invariant g == q + 5*(14 - i);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= i;
  loop invariant g == \at(q, Pre) + 5 * (s - i);
  loop invariant s == 14;
  loop invariant v == s + (s - i)*\at(q, Pre) + 5*((s - i)*(s - i + 1))/2;
  loop invariant g == q + 5*(s - i);
  loop invariant v == s + (s - i) * q + 5 * ((s - i) * (s - i + 1) / 2);
  loop assigns g, v, i;
*/
while (i>0) {
      g = g+5;
      v = v+g;
      i = i-1;
  }

}
