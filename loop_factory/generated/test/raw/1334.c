int main1(int v,int g){
  int s, j;

  s=0;
  j=(v%28)+10;

  while (j>s) {
      j = j - s;
      s = (1)+(s);
      v = v+(s%2);
  }

}
