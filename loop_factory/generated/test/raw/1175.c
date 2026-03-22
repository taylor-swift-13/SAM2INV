int main1(int h){
  int jp, v1y, iy4q, un23;

  jp=(h%60)+60;
  v1y=(h%9)+2;
  iy4q=0;
  un23=0;

  while (jp>v1y*iy4q+un23) {
      if (un23==v1y-1) {
          un23 = 0;
          iy4q++;
      }
      else {
          un23++;
      }
      h = h+(iy4q%5);
  }

}
