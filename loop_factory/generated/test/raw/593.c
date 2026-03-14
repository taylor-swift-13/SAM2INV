int main1(){
  int hbu, dj, auwh;

  hbu=0;
  dj=(1%20)+10;
  auwh=(1%15)+8;

  for (; dj>0&&auwh>0; hbu++) {
      if (hbu%2==0) {
          dj = dj - 1;
      }
      else {
          auwh = auwh - 1;
      }
  }

}
