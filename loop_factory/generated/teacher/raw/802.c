int main1(int a,int b){
  int j, u, v, g;

  j=(b%10)+18;
  u=0;
  v=0;
  g=0;

  while (v<j) {
      if (v<j/2) {
          g = g+3;
      }
      else {
          g = g-3;
      }
      v = v+1;
  }

}
