int main1(int a,int b,int k,int m){
  int l, i, v, j, z, s, y;

  l=a+22;
  i=0;
  v=(a%60)+60;
  j=(a%9)+2;
  z=0;
  s=0;
  y=0;

  while (v>j*z+s) {
      if (s==j-1) {
          s = 0;
          z = z+1;
      }
      else {
          s = s+1;
      }
      v = v+i;
      j = j*j;
      z = z+v*j;
      if ((i%2)==0) {
          s = j+i;
      }
      if ((i%2)==0) {
          y = y*z;
      }
      else {
          j = y*y;
      }
  }

}
