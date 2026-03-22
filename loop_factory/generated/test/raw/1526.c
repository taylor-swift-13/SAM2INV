int main1(){
  int g, q1, w8h, yax, op, m5, p59, x;

  g=1;
  q1=0;
  w8h=0;
  yax=q1;
  op=q1;
  m5=12;
  p59=q1;
  x=g;

  while (1) {
      if (q1%4==1) {
          w8h = w8h + 1;
      }
      else {
          yax += 1;
      }
      if (q1%4==2) {
          op++;
      }
      else {
      }
      m5 = m5 + 1;
      x = (x+w8h)%9;
      p59 += m5;
      m5 = p59-m5;
      q1 = q1 + 1;
      if (q1>=g) {
          break;
      }
  }

}
