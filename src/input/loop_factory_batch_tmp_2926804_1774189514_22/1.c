int main1(int h,int p){
  int h8, i, k6lf, w1, c, f7r, q3, g;

  h8=h+25;
  i=h8;
  k6lf=0;
  w1=0;
  c=0;
  f7r=(h%18)+5;
  q3=i;
  g=0;

  while (f7r>=1) {
      c = c+h*p;
      k6lf = k6lf+h*h;
      w1 = w1+p*p;
      f7r -= 1;
      if (f7r*f7r<=h8+3) {
          p = p*2;
      }
      if ((i%6)==0) {
          g = g%5;
      }
      q3 = q3 + g;
      h = h*4+(f7r%2)+0;
      g += h;
      p = p%9;
      h += 4;
  }

}
