int main1(int t){
  int b, y, yp5;

  b=t;
  y=-13637;
  yp5=b;

  while (y<=-3) {
      y = y+yp5+2;
      yp5 += 2;
      t += yp5;
      t += 1;
  }

}
