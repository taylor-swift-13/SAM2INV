int main1(int a){
  int k, i, qv;

  k=0;
  i=(a%20)+10;
  qv=(a%15)+8;

  for (; i>0&&qv>0; k += 1) {
      if (k%2==0) {
          i--;
      }
      else {
          qv--;
      }
  }

}
