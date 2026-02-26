int main1(int k,int m){
  int j, l, p;

  j=9;
  l=4;
  p=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 9;
  loop invariant l == 4;
  loop invariant k == \at(k,Pre);
  loop invariant m == \at(m,Pre);
  loop invariant p >= 4;
  loop invariant p <= 9;
  loop invariant l <= p;
  loop invariant p <= j;
  loop invariant j == 9 && l == 4 && (p == 4 || p == 5);
  loop invariant p <= 5;
  loop invariant l == 4 && (p == 4 || p == 5) && k == \at(k, Pre) && m == \at(m, Pre);
  loop assigns p;
*/
while (l+5<=j) {
      p = p+3;
      if (p+3<j) {
          p = p+p;
      }
      else {
          p = l%9;
      }
  }

}
