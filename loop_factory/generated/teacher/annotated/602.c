int main1(int b,int m){
  int k, e, i;

  k=12;
  e=k;
  i=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i + e*(e+1)/2 == b + 78;
  loop invariant 0 <= e;
  loop invariant e <= 12;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant i == b + 78 - e*(e+1)/2;
  loop invariant i == \at(b,Pre) + 78 - e*(e+1)/2;
  loop invariant i == \at(b, Pre) + ((12 - e) * (13 + e)) / 2;
  loop invariant e >= 0;
  loop invariant i == b + (k*(k+1))/2 - (e*(e+1))/2;
  loop invariant e <= k;
  loop assigns i, e;
*/
while (e>0) {
      i = i+e;
      e = e-1;
  }

}
