int main1(int a,int b){
  int p, i, e;

  p=(a%14)+4;
  i=p+4;
  e=-5;

  while (i>=p+1) {
      e = e*2;
      e = e*e+e;
      i = i-3;
  }

}
