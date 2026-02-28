int main1(int b,int k){
  int j, m, r;

  j=49;
  m=0;
  r=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 0;
  loop invariant r >= k;
  loop invariant ((r - k) % 2 == 0);
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant j == 49;
  loop invariant (r - k) % 2 == 0;
  loop invariant (7 <= b + j) ==> ((r - k) % 6 == 0);
  loop invariant (7 > b + j) ==> ((r - k) % 4 == 0);
  loop invariant !(7 <= b + j) ==> ((r - k) % 4 == 0);
  loop assigns r;
*/
while (1) {
      r = r+4;
      if (m+7<=b+j) {
          r = r+2;
      }
      r = r+m;
  }

}
