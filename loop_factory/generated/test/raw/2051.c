int main1(){
  int ukt, ki2g, e0id, qfm, pv, y;

  ukt=(1%31)+10;
  ki2g=1;
  e0id=ki2g;
  qfm=0;
  pv=ki2g;
  y=0;

  while (ki2g > 0) {
      y = (ki2g--, qfm += (y + pv) >= ukt, (y + pv) < ukt ? y + pv : y + pv - ukt);
      qfm = qfm + y;
      e0id = e0id*4+2;
      ki2g = 0;
  }

}
