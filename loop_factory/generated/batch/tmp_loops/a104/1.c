int main1(int b,int m){
  int h, n, w;

  h=79;
  n=0;
  w=-2;

  while (n<=h-1) {
      w = w+w;
      if ((n%3)==0) {
          w = w+1;
      }
      n = n+1;
  }

}
