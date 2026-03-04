int main1(int v){
  int ez8;

  ez8=(v%15)+3;

  while (ez8!=0) {
      ez8--;
      v = v + ez8;
  }

}
