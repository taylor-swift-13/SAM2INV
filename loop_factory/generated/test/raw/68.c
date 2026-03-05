int main1(int j,int p){
  int hr, fx;

  hr=j;
  fx=0;

  while (fx<hr) {
      fx = (fx+1)%6;
      fx = fx + 1;
      j += fx;
  }

}
