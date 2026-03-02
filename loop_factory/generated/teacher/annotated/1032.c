int main1(int k,int m){
  int j, d, r;

  j=15;
  d=0;
  r=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 15;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant d >= 0;
  loop invariant r >= 0;
  loop invariant r == d - 1 || (d == 0 && r == 15);
  loop invariant (d==0 ==> r==15) && (d>0 ==> r==d-1);
  loop invariant d >= 0 && r >= 0 && j == 15 && k == \at(k, Pre) && m == \at(m, Pre);
  loop invariant (r + 1 == d) || (r == 15);
  loop invariant (d == 0 && r == 15) || (r == d - 1);
  loop invariant (d == 0 && r == j) || r == d - 1;
  loop invariant j == 15 && k == \at(k, Pre) && m == \at(m, Pre);
  loop invariant (d == 0 && r == 15) || r == d - 1;
  loop invariant (d == 0 && r == 15) || (d > 0 && r == d - 1);
  loop assigns r, d;
*/
while (1) {
      r = r-r;
      if (r+4<j) {
          r = r+d;
      }
      d = d+1;
  }

}
