int main1(int k,int m){
  int g, i, v;

  g=(k%14)+12;
  i=0;
  v=-3;

  while (1) {
      v = v+4;
      if (i+4<=k+g) {
          v = v+3;
      }
  }

}
