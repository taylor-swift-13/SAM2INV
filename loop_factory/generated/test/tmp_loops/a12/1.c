int main1(int y,int l){
  int sl;

  sl=(y%15)+3;

  while (sl!=0) {
      sl -= 1;
      l = l + sl;
  }

}
