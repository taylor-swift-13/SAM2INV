int main1(int t,int f){
  int j;

  j=(f%15)+3;

  while (j!=0) {
      j -= 1;
      t += j;
  }

}
