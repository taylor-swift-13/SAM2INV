int main1(int i){
  int d4, km, f;
  d4=i-9;
  km=0;
  f=km;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d4 == \at(i,Pre) - 9;
  loop invariant f == km;
  loop invariant i == \at(i,Pre) + km*(km+1)/2;
  loop invariant 0 <= km && (km <= d4 || d4 <= 0);
  loop invariant 0 <= km;
  loop invariant i == \at(i, Pre) + km*(km+1)/2 && km >= 0 && (km <= d4 || km == 0);
  loop invariant i == \at(i, Pre) + km*(km+1)/2 && ((d4 <= 0) || (km <= d4));
  loop assigns f, km, i;
*/
while (1) {
      if (!(km<d4)) {
          break;
      }
      f = f + 1;
      km = km + 1;
      i += km;
  }
}