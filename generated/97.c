int main97(int b){
  int cd, sy, m5b, m2c, ml, rdt, y;

  cd=b;
  sy=0;
  m5b=sy;
  m2c=b;
  ml=sy;
  rdt=cd;
  y=cd;

  while (1) {
      rdt = rdt + 1;
      m2c--;
      y += sy;
      m5b += 1;
      if (m5b<ml+5) {
          ml += rdt;
      }
      sy += 1;
      if (sy>=cd) {
          break;
      }
  }

}
