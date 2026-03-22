int main1(int w){
  int q, yly9, y49a, ml6, p4, h3w;

  q=(w%40)+8;
  yly9=3;
  y49a=0;
  ml6=(w%28)+10;
  p4=q;
  h3w=yly9;

  while (1) {
      if (!(ml6>y49a)) {
          break;
      }
      ml6 = ml6 - y49a;
      h3w++;
      w = w+q-yly9;
      y49a = y49a + 1;
      p4 = (3)+(p4);
  }

  while (1) {
      if (!(ml6>0)) {
          break;
      }
      y49a = y49a+w*w;
      yly9 = yly9+w*w;
      h3w = h3w+w*w;
      ml6 -= 1;
      w = w+(y49a%9);
  }

}
