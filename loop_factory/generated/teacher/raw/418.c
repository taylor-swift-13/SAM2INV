int main1(int k,int n){
  int v, e, a;

  v=k+8;
  e=1;
  a=e;

  while (e*3<=v) {
      a = a+2;
      a = a%3;
      if ((e%5)==0) {
          a = a*a+a;
      }
  }

}
