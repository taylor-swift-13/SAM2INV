int main1(int k,int p){
  int h, t, g;

  h=(k%7)+4;
  t=0;
  g=k;

  while (t<=h-1) {
      g = g+1;
      g = g+t;
      t = t+1;
  }

}
