int main1(int k,int m){
  int l, r, i;

  l=10;
  r=l;
  i=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 40 - 3*r && 0 <= r && r <= 10;
  loop invariant l == 10 && k == \at(k, Pre) && m == \at(m, Pre);
  loop invariant r >= 0 && r <= 10;
  loop invariant l == 10;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant r >= 0;
  loop invariant i == 40 - 3*r;
  loop invariant i + 3*r == 40;
  loop invariant i <= 40;
  loop assigns i, r;
*/
while (r>0) {
      if (i+6<l) {
          i = i+i;
      }
      i = i+3;
      r = r-1;
  }

}
