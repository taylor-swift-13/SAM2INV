int main1(){
  int l, j, fy, o;
  l=54;
  j=1;
  fy=4;
  o=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == (j - 1) % 5;
  loop invariant l == 54;
  loop invariant fy >= 0;
  loop invariant fy >= o;
  loop invariant 1 <= j <= l;
  loop assigns o, j, fy;
*/
while (j<l) {
      o = j%5;
      if (j>=fy) {
          fy = (j-fy)%5;
          fy = fy+o-fy;
      }
      else {
          fy = fy + o;
      }
      j++;
      fy++;
  }
}