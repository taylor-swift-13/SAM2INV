int main1(int i){
  int m, j6y, vvi, rx3y;
  m=i+24;
  j6y=0;
  vvi=0;
  rx3y=j6y;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == \at(i, Pre) + m * vvi;
  loop invariant rx3y <= vvi;
  loop invariant rx3y == 0;
  loop assigns i, vvi, rx3y;
*/
while (vvi<m) {
      vvi += 1;
      if (!(!(vvi<=rx3y))) {
          rx3y = vvi;
      }
      i = i + m;
  }
}