int main1(int a,int k){
  int j, h, y;

  j=a-3;
  h=0;
  y=h;

  while (1) {
      y = y+2;
      if ((h%6)==0) {
          y = y+y;
      }
      y = y+h;
  }

}
