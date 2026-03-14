int main1(int x){
  int ar9, ye, d5rm, f, o2;
  ar9=56;
  ye=0;
  d5rm=0;
  f=x;
  o2=ar9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ye == d5rm % 8;
  loop invariant ar9 == 56;
  loop invariant o2 == 56;
  loop invariant 0 <= d5rm;
  loop invariant d5rm <= ar9;
  loop invariant f == x + d5rm*(o2 + x) + 28*(d5rm/8) + ((d5rm%8)*((d5rm%8)+1))/2;
  loop invariant f == \at(x, Pre) + d5rm*(o2 + x) + 28*(d5rm/8) +
                   ((d5rm%8) * ((d5rm%8) + 1)) / 2;
  loop assigns ye, d5rm, f;
*/
while (d5rm<ar9) {
      ye = (ye+1)%8;
      d5rm++;
      f += ye;
      f = f+o2+x;
  }
}