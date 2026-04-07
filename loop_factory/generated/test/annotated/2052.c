int main1(){
  int ukt, ki2g, e0id, qfm, pv, y;
  ukt=(1%31)+10;
  ki2g=1;
  e0id=ki2g;
  qfm=0;
  pv=ki2g;
  y=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pv == 1;
  loop invariant e0id == 1 + 5 * (1 - ki2g);
  loop invariant (ki2g >= 0 && ki2g <= 1);
  loop invariant qfm == (1 - ki2g);
  loop invariant y == (1 - ki2g);
  loop invariant ( (ki2g == 1 && y == 0 && qfm == 0 && e0id == 1)
                    || (ki2g == 0 && y == 1 && qfm == 1 && e0id == 6) );
  loop invariant ukt == 11;
  loop assigns y, qfm, e0id, ki2g;
*/
while (ki2g > 0) {
      y = (ki2g--, qfm += (y + pv) >= ukt, (y + pv) < ukt ? y + pv : y + pv - ukt);
      qfm = qfm + y;
      e0id = e0id*4+2;
      ki2g = 0;
  }
}