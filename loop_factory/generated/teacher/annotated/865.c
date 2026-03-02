int main1(int k,int p){
  int r, c, v;

  r=k-5;
  c=0;
  v=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == k - 5;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant 0 <= c;

  loop invariant r == \at(k, Pre) - 5;
  loop invariant c >= 0;

  loop invariant (c == 0) ==> (v == -3);
  loop invariant (c > 0) ==> (v % 2 == 0);

  loop invariant k == \at(k, Pre) && p == \at(p, Pre) && r == \at(k, Pre) - 5;
  loop invariant (r < 0) || (0 <= c && c <= r)
                   && ( (c==0 ==> v % 8 == -3)
                        && (c==1 ==> v % 8 == -6)
                        && (c==2 ==> v % 8 == -4)
                        && (c>=3 ==> v % 8 == 0) );
  loop invariant r == k - 5 && p == \at(p, Pre) && k == \at(k, Pre) && 0 <= c;
  loop invariant v <= 0 && (c <= r || r < 0);
  loop assigns c, v;
*/
while (c<=r-1) {
      v = v+v;
      if (v+7<r) {
          v = v%8;
      }
      c = c+1;
  }

}
