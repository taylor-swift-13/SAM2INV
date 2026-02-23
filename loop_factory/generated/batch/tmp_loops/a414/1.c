int main1(int k,int m){
  int g, i, v;

  g=(k%14)+12;
  i=g;
  v=k;

  while (i>=4) {
      if ((i%2)==0) {
          v = v*v+v;
      }
      i = i-4;
  }

}
