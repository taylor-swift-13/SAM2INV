int main1(){
  int n2f, ow4, ko5, o7;
  n2f=10;
  ow4=0;
  ko5=0;
  o7=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ow4 == n2f - o7*(o7 + 1)/2;
  loop invariant o7 >= 0;
  loop invariant n2f == 10;
  loop invariant ko5 == ((4 - o7) * (5 - o7) * (9 + o7)) / 6;
  loop invariant o7 <= 4;
  loop assigns ow4, ko5, o7;
*/
while (ow4 < n2f) {
      ow4 += o7;
      ko5 += ow4;
      o7 -= 1;
  }
}