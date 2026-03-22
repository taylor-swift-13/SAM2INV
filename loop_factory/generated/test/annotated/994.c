int main1(){
  int v7, gydl, x;
  v7=1+23;
  gydl=0;
  x=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == gydl * (gydl - 1) / 2;
  loop invariant 0 <= gydl <= v7;
  loop assigns x, gydl;
*/
while (1) {
      x += gydl;
      gydl = gydl + 1;
      if (gydl>=v7) {
          break;
      }
  }
}