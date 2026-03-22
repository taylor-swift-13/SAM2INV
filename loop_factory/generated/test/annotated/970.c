int main1(){
  int ov, de, ui;
  ov=(1%20)+5;
  de=(1%20)+5;
  ui=(1%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ov == de;
  loop invariant 0 <= ov <= 6;
  loop invariant ui >= de;
  loop assigns ov, de, ui;
*/
while (ov>0) {
      if (de>0) {
          if (ui>0) {
              ov -= 1;
              de--;
              ui--;
          }
      }
      ui += ui;
  }
}