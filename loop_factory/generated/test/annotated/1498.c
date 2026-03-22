int main1(){
  int v6, e3, v0c, j, h;
  v6=10;
  e3=0;
  v0c=1;
  j=0;
  h=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e3 <= v6;
  loop invariant v0c == h;
  loop invariant j == 2*h - 2;
  loop invariant 0 <= e3;
  loop assigns e3, v0c, j, h;
*/
while (e3 < v6) {
      e3 += 1;
      v0c += h;
      j = j + v0c;
      h = h * 2;
  }
}