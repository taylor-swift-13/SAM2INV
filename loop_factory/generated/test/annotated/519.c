int main1(int h,int z){
  int hm, kb, v7d;
  hm=(z%20)+5;
  kb=(z%20)+5;
  v7d=(z%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hm == kb;
  loop invariant kb == v7d;
  loop invariant hm <= ((\at(z, Pre) % 20) + 5);
  loop assigns h, hm, kb, v7d;
*/
while (1) {
      if (!(hm>0)) {
          break;
      }
      if (kb>0) {
          if (v7d>0) {
              hm--;
              kb -= 1;
              v7d--;
          }
      }
      h = h + v7d;
  }
}