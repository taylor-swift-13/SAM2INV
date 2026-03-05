int main1(int o){
  int lu, ou3, it;

  lu=(o%17)+17;
  ou3=1;
  it=lu;

  while (ou3+1<=lu) {
      if (ou3<lu/2) {
          it = it + it;
      }
      else {
          it += 1;
      }
      o = o + lu;
  }

}
