int main1(int k,int m){
  int p, i, v, u;

  p=k-5;
  i=0;
  v=k;
  u=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v + u == \at(k, Pre) + \at(m, Pre);
  loop invariant i >= 0;
  loop invariant i <= p || p < 0;
  loop invariant k == \at(k, Pre) && m == \at(m, Pre);
  loop invariant v == \at(k, Pre) + i;

  loop invariant u == \at(m, Pre) - i;
  loop invariant 0 <= i && (p < 0 || i <= p);
  loop invariant p == \at(k, Pre) - 5;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant v - i == \at(k, Pre);
  loop invariant u + i == \at(m, Pre);

  loop invariant k == \at(k, Pre) && m == \at(m, Pre) && p == \at(k, Pre) - 5;

  loop invariant 0 <= i;
  loop invariant v - i == \at(k, Pre) && v + u == \at(k, Pre) + \at(m, Pre);

  loop invariant v == \at(k, Pre) + i && u == \at(m, Pre) - i && p == \at(k, Pre) - 5;
  loop assigns v, u, i;
*/
while (i<=p-1) {
      v = v+1;
      u = u-1;
      i = i+1;
  }

}
