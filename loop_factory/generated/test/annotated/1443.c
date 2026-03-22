int main1(){
  int z, i3, y55, ck;
  z=(1%40)+4;
  i3=0;
  y55=0;
  ck=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ck == 5 - i3;
  loop invariant y55 == 5*i3 - (i3*(i3-1))/2;
  loop invariant i3 + ck == z;
  loop invariant 0 <= i3 <= z;
  loop assigns y55, i3, ck;
*/
while (i3<z&&ck>0) {
      y55 += ck;
      i3 = i3 + 1;
      ck = ck - 1;
  }
}